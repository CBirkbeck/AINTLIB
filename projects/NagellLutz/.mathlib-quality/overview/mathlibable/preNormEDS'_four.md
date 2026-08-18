# /mathlibable report — `preNormEDS'_four`

**Verdict: NO-mathlib-has-it** — the declaration is a byte-for-byte fork of an existing
mathlib lemma.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note; reasoning from source — the
                            decl is a forked copy of a green mathlib lemma, so elaboration is not in doubt)
- decl `preNormEDS'_four`:  ✓ resolved at
                            `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:755`
- kind:                     lemma (`@[simp]`)
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences (EDS) and the construction of
                            normalised EDSs from initial terms." The file is a near-verbatim FORK of
                            `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same copyright
                            header — © 2024 David Kurniadi Angdinata — same author, same `section
                            PreNormEDS`).

**Qualified name.** The decl lives in `section PreNormEDS` (opens at line 704), which contains **no**
`namespace`. So the qualified name is the bare `preNormEDS'_four` — there is no namespace prefix.
(`variable (b c d : R)` is a section variable, not a namespace.) Verified against the file's
`namespace`/`section`/`end` scan.

---

### Statement (Phase 1)

`preNormEDS'_four` states that the auxiliary normalised-EDS sequence `preNormEDS' b c d : ℕ → R`
takes the value `d` at index `4`:

```lean
@[simp]
lemma preNormEDS'_four : preNormEDS' b c d 4 = d := by
  rw [preNormEDS']
```

`preNormEDS'` is the recursively-defined auxiliary sequence for a normalised elliptic divisibility
sequence over a commutative ring `R`, with seed values `W(0)=0, W(1)=1, W(2)=1, W(3)=c, W(4)=d` and
parameter `b`. This lemma is simply the **defining-equation/unfolding lemma** for the fourth seed
value: it reads off the `| 4 => d` arm of the pattern match in `def preNormEDS'`. The proof
`rw [preNormEDS']` unfolds one step of the definition; the value is `d` by definition (`rfl`-class).

- Variables / typeclasses: `{R : Type*} [CommRing R]` (from the file's `variable` block);
  `(b c d : R)` section parameters.
- Hypotheses: none.
- Conclusion (math): the 4th term of the seed of `preNormEDS'` equals `d`.
- Conclusion (Lean): `preNormEDS' b c d 4 = d`.

This is one of a family of five identical glue lemmas: `preNormEDS'_zero/_one/_two/_three/_four`,
each unfolding one seed value, plus the integer-indexed `preNormEDS_zero … _four`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a definitional-unfolding glue lemma (`@[simp]` `rw [def]`) for one seed value of a sequence;
not a structure, not a named theorem, not a main result.

### One-line check (Phase 2b)

Body line count: 1 substantive line (`rw [preNormEDS']`). Kind is `lemma`, so the def-oriented
one-liner exemption table is **n/a** — this section is informational only. It is, however, the
archetypal glue lemma (a definitional unfolding), which under the skill's verdict-inheritance rule is
itself a strong "do not add separately" signal: its content is wholly determined by the parent
`def preNormEDS'`.

---

### Literature search (Phase 3)

For a definitional-unfolding lemma the "literature-standard form" is just *the definition of the
sequence at index 4*. There is no independent mathematical content to locate in the literature — the
statement `preNormEDS' b c d 4 = d` is true purely because Angdinata's recursive definition assigns
`d` to its fourth seed. The relevant "source" is therefore the definition itself, which already lives
in mathlib. The channels below are recorded for completeness; the WebSearch hit confirms the concept
and its mathlib home directly.

| #  | Channel                           | Query                                                                 | Hit? | Standard form found                          | Notes |
|----|-----------------------------------|-----------------------------------------------------------------------|------|----------------------------------------------|-------|
|  1 | WebSearch (specific form)         | "preNormEDS mathlib elliptic divisibility sequence … Angdinata"       | yes  | `preNormEDS'` seed `W(0..4)=0,1,1,c,d`, param `b` | Top hit = the mathlib docs page for `Mathlib.NumberTheory.EllipticDivisibilitySequence`; confirms the auxiliary sequence and its seed values verbatim |
|  2 | WebSearch (general form)          | (same query, generality angle on normalised EDS construction)         | yes  | `normEDS` defined via `preNormEDS (b^4) c d`  | The construction (Shipsey/Stange-style normalised EDS from seeds) — the *recursion* is the math; an individual seed-readoff is not a literature result |
|  3 | WebSearch (named-after / aliases) | EDS auxiliary / "pre-normalised" sequence seed values                  | yes  | arXiv 2604.05280 "On Elliptic Sequences over Commutative Rings"; arXiv math/0402415 (Stange/Ward EDS) | Background on EDS over rings; none state a standalone "4th seed = d" lemma — it is definitional |
|  4 | ChatGPT MCP                       | n/a — not consulted                                                    | n/a  | —                                            | Deliberately skipped: the decl is a verbatim fork of a mathlib `rw [def]` glue lemma; a second opinion on "is the 4th seed equal to d" adds nothing and the mathlib-has-it evidence is already conclusive |
|  5 | Local references                  | grep `.mathlib-quality/references/`                                    | n/a  | (directory absent)                           | `projects/NagellLutz/.mathlib-quality/references/` does not exist — recorded n/a |
|  6 | nLab                              | "elliptic divisibility sequence"                                      | n/a  | —                                            | nLab has no EDS page; not a categorical concept — n/a |
|  7 | nCatLab                           | —                                                                     | n/a  | —                                            | Not a categorical concept — n/a |
|  8 | Stacks Project                    | —                                                                     | n/a  | —                                            | Not an algebraic-geometry / scheme-theoretic concept (it is an arithmetic recurrence) — n/a |
|  9 | MathOverflow / Math.SE            | EDS auxiliary sequence seed values                                    | n/a  | —                                            | No discussion of a standalone seed-readoff identity; definitional — n/a |
| 10 | recent arXiv (last 5 years)       | EDS over commutative rings                                            | yes  | arXiv 2604.05280                              | Confirms the area is active; no standalone "4th seed" lemma (it would be definitional in any such paper) |

### Literature summary (Phase 3)

Concept identified as: the **auxiliary sequence `preNormEDS'` for a normalised elliptic divisibility
sequence** (Angdinata's mathlib formalisation; rooted in Shipsey/Stange/Ward EDS theory).
Sources agree on the standard form: yes — the seed `W(0..4) = 0, 1, 1, c, d` with parameter `b` is
exactly what the mathlib docs and the EDS literature use.
Most general standard form: `preNormEDS' b c d 4 = d` is not an independent theorem; it is the 4th
arm of the recursive **definition**. There is no "more general" version to seek — generalising the
ring `R` is already maximal (`CommRing R`, see Phase 4).
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

### 4a. Generality status table

Literature-standard form: the seed value of `preNormEDS'` at 4, over a commutative ring.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `{R : Type*} [CommRing R]` | commutative ring | commutative ring (EDS are defined over CommRing) | NO | `preNormEDS'` is defined over `CommRing R`; the seed read-off holds at exactly that generality. Matches mathlib's own `preNormEDS'`. |
| 2 | `(b c d : R)` | ring elements | ring elements | NO | These ARE the defining seed parameters; nothing to weaken. |

### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL** (identical to mathlib's own `preNormEDS'_four`).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### 4c. Modern mathlib-idiom check

| # | Question | Applies? | Reason |
|---|----------|----------|--------|
| 1 | bundled hyps → typeclasses? | no | already a bare `CommRing` typeclass; no "let X be a foo" preamble |
| 2 | sequences/metric → filters/topology? | no | this is a discrete arithmetic recurrence; no analytic notion to filter-ise |
| 3 | construction → universal-property class? | no | a seed read-off, not a construction |
| 4 | set+closure-pred → bundled substructure? | no | not a substructure |
| 5 | vector-space/field-specific → weaken typeclass? | no | already `CommRing`, the natural home for EDS |
| 6 | 1-categorical → higher-categorical? | no | not categorical |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive structure? | no | the index `4 : ℕ` is a literal seed position; generalising it is meaningless (it names a specific recursion arm) |

Modern idiom available: **no**. The form is already the idiomatic mathlib one — because it **is** the
mathlib decl, verbatim.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `preNormEDS'_four` (Phase 5)

[A] Lean-Finder       n/a (mathlib index unavailable for direct query this run; resolved by grep below)
[B] Loogle            type pattern `preNormEDS' _ _ _ 4 = _`       resolved by direct source grep instead
[C] LeanSearch        "value of auxiliary normalised EDS sequence at four"   resolved by direct source grep instead
[D] Grep mathlib src  `grep -n "preNormEDS'_four" …/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
                      → **HIT at line 157** (and the whole `preNormEDS'_zero…_four` family at 141–158;
                      `def preNormEDS'` at 124)
[E] Name pattern      `preNormEDS'_four`                            → exact name match in mathlib

Searched for both the user's current form and the (identical) literature-standard form.

**Concluded: found in mathlib as `preNormEDS'_four`; IDENTICAL form** — byte-for-byte:

mathlib (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:156-158`):
```lean
@[simp]
lemma preNormEDS'_four : preNormEDS' b c d 4 = d := by
  rw [preNormEDS']
```
project (`EllipticDivisibilitySequence.lean:754-756`): same three lines, same `@[simp]`, same proof.
Both in a non-namespaced `section PreNormEDS`, both under `variable (b c d : R)` with `[CommRing R]`.
The project file shares mathlib's exact copyright header (© 2024 David Kurniadi Angdinata) — it is a
direct fork. The only divergence in the surrounding file is the *definition* `preNormEDS'`: the
project version inlines explicit `have h4/h3/h2/h1 : … < n+5` termination proofs where mathlib uses
`gcongr`, but the **lemma statement and proof are identical**.

---

### Composition check (Phase 6)

### 6.0. Call sites — `preNormEDS'_four`

Internal use count (project, excluding the declaring file): **1**
External-to-file callers: **1** distinct file.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:97` | `preNormEDS'_four ..` |
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1127` | `| four => rw [preNormEDS'_four, preNormEDS'_four]` (same file — not counted in the "1") |

(There is also a second forked copy of the entire file, `EllipticDivisibilitySequenceOriginal.lean`,
with its own `preNormEDS'_four` at line 709 and use at 1074 — a parallel duplicate track, not a
consumer of this decl.)

Inline-derivation grep: the same `= d` fact is re-`rw`-derived inside the sibling file
`EllipticDivisibilitySequenceOriginal.lean`; that is a whole-file duplicate, not an independent
inlining.

The call sites are exactly the call sites mathlib's own `preNormEDS'_four` would serve — confirming
the decl is redundant with mathlib, not a project-specific specialisation.

### 6a. Composition attempt

Can `preNormEDS'_four` be derived from mathlib in ≤3 chained calls? It does not need composition —
mathlib has the **identical lemma**. The "derivation" is literally `Mathlib...preNormEDS'_four`
itself (and the project decl's own proof `rw [preNormEDS']` is the one-step unfolding, also already
in mathlib).

Conclusion: **NOT-COMPOSABLE in the building-block sense — because it is already a single named
mathlib lemma (the stronger NO-mathlib-has-it case applies, not NO-composable).**

---

## Verdict: `preNormEDS'_four`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): the concept (`preNormEDS'` auxiliary normalised-EDS sequence) maps
  directly to mathlib; the "4th seed = d" statement is definitional, not an independent literature
  result.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — identical to mathlib's form; no modern-idiom
  improvement (it *is* the idiom).
- Mathlib search (Phase 5): **found in mathlib as `preNormEDS'_four`, byte-for-byte identical**
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:157`), `@[simp]`, proof `rw [preNormEDS']`.
- Composition check (Phase 6): not needed — mathlib has the exact named lemma.

**Rationale.**
The project's `EllipticDivisibilitySequence.lean` is a direct fork of mathlib's
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` — same © 2024 David Kurniadi Angdinata
header, same `section PreNormEDS`, same `def preNormEDS'` seed `W(0..4) = 0,1,1,c,d`. The lemma
`preNormEDS'_four` is reproduced verbatim: identical statement (`preNormEDS' b c d 4 = d`), identical
`@[simp]` attribute, identical proof (`rw [preNormEDS']`), identical typeclass context (`CommRing R`).
There is nothing to upstream — mathlib already owns this exact declaration. The fork exists because
the project (per the task's note) forks the EDS / division-polynomial machinery to extend it for the
Nagell–Lutz development; the surrounding `def preNormEDS'` differs only in its termination-proof
plumbing (explicit `have … omega` vs. mathlib's `gcongr`), which does not affect this lemma.

**WHY not (refactor-actionable).**
Mathlib already has it, verbatim. The project does not need to re-declare it: every use site can call
the mathlib lemma directly. Because the whole file is a fork, the right fix is not a one-line swap of
this single lemma but **deduplicating the forked `PreNormEDS` block against upstream mathlib** — i.e.
delete the local `preNormEDS'` definition + its seed-unfolding lemmas (`preNormEDS'_zero…_four`,
`preNormEDS'_even/_odd`, and the `preNormEDS_*` family) and `import
Mathlib.NumberTheory.EllipticDivisibilitySequence` instead, keeping only the genuinely-new material
the fork adds on top. This is exactly the kind of cross-project dedup the AINTLIB cleanup lane owns.

Existing mathlib decl:        `preNormEDS'_four`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:157`
Our form follows in 0 lines (it is the same lemma):
```lean
-- after `import Mathlib.NumberTheory.EllipticDivisibilitySequence`, the name resolves directly:
example (R) [CommRing R] (b c d : R) : preNormEDS' b c d 4 = d := preNormEDS'_four
```
Call sites in this project (from Phase 6.0): 1 external (`DivisionPolynomial.lean:97`) + 1 in-file
(`EllipticDivisibilitySequence.lean:1127`); plus the duplicate-file track in
`EllipticDivisibilitySequenceOriginal.lean`.

**Refactor plan:**
1. Prefer the mathlib `PreNormEDS` API over the local fork: where the project re-defines
   `preNormEDS'` and friends, replace the forked block with `import
   Mathlib.NumberTheory.EllipticDivisibilitySequence` and drop the duplicated definitions + the
   `preNormEDS'_zero…_four` (and `preNormEDS_*`) glue lemmas.
2. The call sites (`DivisionPolynomial.lean:97` `preNormEDS'_four ..`, and
   `EllipticDivisibilitySequence.lean:1127` `rw [preNormEDS'_four, …]`) then resolve to the mathlib
   lemma unchanged — same name, same signature, same `@[simp]` behaviour, so no edit is required at
   the call sites themselves once the import is in place.
3. Resolve the `EllipticDivisibilitySequence.lean` vs `EllipticDivisibilitySequenceOriginal.lean`
   double-fork (two copies of this same lemma) as part of the same dedup.
   *Caveat:* the fork keeps a local `preNormEDS'` whose **termination proof** differs from mathlib's;
   confirm nothing downstream depends on the local definitional plumbing before deleting (the lemma
   *statements* are defeq-identical, so consumers of the lemmas are safe).

**Next action:** treat as a cross-project **deduplication** cleanup ticket — delete the forked
`preNormEDS'`/`preNormEDS` seed lemmas (including `preNormEDS'_four`) and import the mathlib module;
do NOT open a mathlib PR (mathlib already has the identical declaration).

---

## Next step

Delete `preNormEDS'_four` (and the surrounding forked `PreNormEDS` seed-lemma block) from the
project and import `Mathlib.NumberTheory.EllipticDivisibilitySequence`; the 1 external + 1 in-file
call sites resolve to the identical mathlib lemma unchanged. No mathlib PR — it is already there.
