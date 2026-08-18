# /mathlibable report — `normEDS_ofNat`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz theorem; elliptic
> curves; division polynomials; elliptic divisibility sequences).
> Declaration: `normEDS_ofNat` at
> `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:897`.

## TL;DR

**Verdict: `NO-mathlib-has-it`.** This file is a near-verbatim *fork* of
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. The lemma
`normEDS_ofNat` exists in current mathlib **at the same namespace position, with
a character-for-character identical statement and the same `@[simp]` attribute**,
at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:293`. Only the proof
tactic differs (irrelevant to mathlibability). This is the consolidation-monorepo
"duplicated mathlib file" pattern, not a novel contribution.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); reasoned from source. The identical statement is already in mathlib, so it elaborates upstream.
- decl `normEDS_ofNat`:     ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:897`
- kind:                     lemma (`@[simp]`)
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences" — defines EDSs and constructs normalised EDSs from initial terms (`preNormEDS'`, `preNormEDS`, `normEDS`, `complEDS`).

**Qualified-name verification.** The lemma sits inside `section NormEDS` (opened
at line 881), which is a `section`, not a `namespace`. The whole file is wrapped
in `@[expose] public section` (line 81), again not a namespace. Walking back
through all enclosing scopes from line 897, there is **no enclosing `namespace`**:
the nearest `namespace EllSequence` (line 90) is closed at line 597, far above
line 897. Hence the fully qualified name is exactly **`normEDS_ofNat`** (no
prefix). This matches the parsed name in the task.

---

### Statement (Phase 1)

`normEDS_ofNat` is a **rewrite/`simp` lemma** re-expressing `normEDS` on a
**natural-number** index `↑n` via the `ℕ`-indexed auxiliary `preNormEDS'` rather
than the `ℤ`-indexed `preNormEDS`.

Math: for a commutative ring `R`, fixed `b, c, d : R`, and `n : ℕ`,
```
normEDS b c d n = preNormEDS' (b^4) c d n · (if Even n then b else 1).
```
Since `normEDS b c d m := preNormEDS (b^4) c d m · (Even m ? b : 1)` by definition
(`m : ℤ`), and `preNormEDS (b^4) c d ↑n = preNormEDS' (b^4) c d n` on `ℕ`-casts
(`preNormEDS_ofNat`), this lemma is the definition specialised to a `ℕ`-cast index
with the auxiliary swapped to its `ℕ`-form. Purpose: purely a normalisation/`simp`
bridge so concrete naturals evaluate via the structurally-recursive `preNormEDS'`.

Variables / typeclasses: `{R : Type u} [CommRing R]`, `(b c d : R)`, `(n : ℕ)`.
Hypotheses: none.
Conclusion (Lean): `normEDS b c d ↑n = preNormEDS' (b ^ 4) c d n * if Even ↑n then b else 1`.

Project proof (line 898–899): `simp_rw [normEDS, preNormEDS_ofNat, Int.even_coe_nat]`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** — a `@[simp]` glue/normalisation lemma; not a named theorem,
not a new structure, not a `## Main results` entry.
(Note: lit width is exhaustive-by-protocol regardless — but a same-name,
identical-statement mathlib hit, found by direct file comparison, is the strongest
possible NO signal and dominates the verdict honestly; see Phase 5.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` — **n/a**.

---

### Literature search (Phase 3)

**Override note.** Phase 5 returns the single strongest NO signal: mathlib has a
lemma of the **same name** (`normEDS_ofNat`), in the **same namespace position**
(`section NormEDS`), with a **character-identical statement** and the same
`@[simp]` attribute, in a file the project has **forked wholesale**. Per the
skill's logic, `NO-mathlib-has-it` requires Phase 5 = "found in mathlib …;
identical form", which is satisfied maximally; no nine-channel lit sweep can
change a verdict that follows from a direct file diff. The table is recorded for
completeness; channels that could only matter for a YES/generalise verdict are
`n/a — moot (exact same-name mathlib hit; see Phase 5)`.

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence" `normEDS` `preNormEDS` Lean mathlib | yes (concept) | EDS per Ward's memoir; mathlib's `normEDS` is the canonical normalised EDS | Concept (EDS) is classical (Ward 1948); this *lemma* is mathlib-internal API normalisation, not a named literature result. |
|  2 | WebSearch (general form)         | "normalised elliptic divisibility sequence" recurrence natural index | yes (concept) | normalised EDS with `W(1)=1, W(2)=b, W(3)=c, W(4)=db` | matches mathlib `normEDS` initial-value convention; the `ℕ`-vs-`ℤ` split is a formalisation detail, not mathematics. |
|  3 | WebSearch (named-after/aliases)  | "Ward elliptic divisibility sequence" division polynomial | yes (concept) | Ward, *Memoir on Elliptic Divisibility Sequences* (in the file's own References) | confirms the umbrella concept is standard; says nothing about this glue lemma as a separate object. |
|  4 | ChatGPT MCP                      | (MCP down per task env note) | n/a | — | Fallback to WebSearch + direct mathlib file comparison, which is authoritative here. |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/` | n/a — moot | — | Even a perfect reference hit cannot override a same-name identical mathlib decl. |
|  6 | nLab                             | "elliptic divisibility sequence" | n/a — moot | — | nLab has only concept-level material; no page for this formalisation lemma. |
|  7 | nCatLab (categorical)            | — | n/a | — | Not a categorical concept. |
|  8 | Stacks Project (alg geom)        | — | n/a | — | EDS/division-polynomial recurrences are outside Stacks' scheme-theoretic scope. |
|  9 | MathOverflow / MSE              | "elliptic divisibility sequence parity recurrence" | n/a — moot | — | Concept discussed; this is a library-internal normalisation, not an MO-level question. |
| 10 | recent arXiv (last 5y)          | "elliptic divisibility sequence" division polynomial formalisation | n/a — moot | — | The relevant work (Angdinata et al. on mathlib's EDS/division polynomials) *is* the mathlib code itself. |

### Literature summary (Phase 3)

Concept: **(normalised) elliptic divisibility sequence**, classical (Ward 1948);
`normEDS`/`preNormEDS`/`preNormEDS'` are mathlib's specific formalisation (D. K.
Angdinata et al.). The `ℕ`-vs-`ℤ` auxiliary split (`preNormEDS'` vs `preNormEDS`)
is a **formalisation device**, not a separate mathematical statement. Disagreement
with the literature: none — and irrelevant: this lemma *is* the mathlib API,
copied into the project.

---

### Generality analysis (Phase 4)

Literature-standard form: EDS over a commutative ring `R`. The lemma already uses
the maximally general `[CommRing R]`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring | NO | `normEDS`/`preNormEDS'` need ring structure (the `b^4` factor, the parity branch); exactly mathlib's generality. |
| 2 | `(b c d : R)` | three ring elements | three ring elements | NO | the defining data of the sequence. |
| 3 | `(n : ℕ)` | natural index | natural index | NO (intentional) | the lemma's entire point is the `ℕ`-cast specialisation feeding `preNormEDS'`; generalising the index defeats it (the `ℤ` form is `normEDS_def`). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** — identical to mathlib's, already at
`CommRing`. No weakening opportunities (K = 0).

### Modern-idiom check (Phase 4c)

Modern idiom available: **no**. A finite normalisation/`simp` lemma over a
`CommRing` with a `ℕ`-cast index: no topology to filter-ise, no universal property
to abstract, no substructure to bundle. Mathlib's own form *is* the modern idiom
(it is the upstream lemma). All Phase-4c rows answer `no`.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (introduces no definitional equalities or
typeclass-search paths).

---

### Mathlib search-status: `normEDS_ofNat`

[A] Lean-Finder       "normEDS natural index preNormEDS'"   → hit (concept), superseded by [D]
[B] Loogle            `normEDS _ _ _ ↑_ = preNormEDS' _ _ _ _ * _`  → matches the mathlib lemma
[C] LeanSearch        "normEDS on a natural number equals preNormEDS' times parity factor"  → hit: `normEDS_ofNat`
[D] Grep mathlib src  `grep -rn "normEDS_ofNat" .lake/packages/mathlib/Mathlib`
      → **HIT**: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:293`
[E] Name pattern      exact name `normEDS_ofNat` present in mathlib

**Searched for both** the current form and the (identical) literature/idiomatic
form — they coincide.

Side-by-side (authoritative — this is a forked file):

| | Project (`...:897`) | Mathlib (`...:293`) |
|---|---|---|
| name | `normEDS_ofNat` | `normEDS_ofNat` |
| attr | `@[simp]` | `@[simp]` |
| scope | `section NormEDS` (no namespace) | `section NormEDS` (no namespace) |
| statement | `normEDS b c d ↑n = preNormEDS' (b ^ 4) c d n * if Even ↑n then b else 1` | `normEDS b c d ↑n = preNormEDS' (b ^ 4) c d n * if Even ↑n then b else 1` |
| `def normEDS` directly above? | yes (line 890) | yes (line 289) |
| copyright header | "David Kurniadi Angdinata" | "David Kurniadi Angdinata" |
| proof | `simp_rw [normEDS, preNormEDS_ofNat, Int.even_coe_nat]` | `simp [normEDS]` |

The statements are **character-for-character identical**. The only difference is
the proof tactic, which has no bearing on mathlibability (mathlib already contains
the statement).

Concluded: **"found in mathlib as `normEDS_ofNat`; identical form"** (same name,
same namespace position, same `@[simp]` attribute, same coefficient generality).

---

### Composition check (Phase 6)

#### Call sites — `normEDS_ofNat`

Internal use count: **0** (within `projects/`, excluding the declaring file —
`grep -rn "normEDS_ofNat" projects --include=*.lean` returns only line 897).
External-to-file callers: 0 distinct files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none) | — |

Inline-derivation grep: (none). As a `@[simp]` lemma it is consumed by `simp`
automation, not by explicit name, so a zero by-name count is expected and is *not*
a dead-code signal (it backs the downstream `normEDS_zero/one/two/three/four`
value lemmas via `simp`).

Composition: not needed — mathlib already has the exact lemma verbatim. (For the
record, even from primitives it is a one-liner: `by simp [normEDS]` from the
`normEDS` definition plus `preNormEDS_ofNat` / `Int.even_coe_nat`, all in mathlib.)

Conclusion: **N/A — mathlib has the exact lemma** (the `NO-mathlib-has-it` signal
dominates `NO-composable`).

---

## Verdict: `normEDS_ofNat`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): concept (EDS) is classical; this specific lemma is
  a mathlib-internal normalisation step — moot given the Phase-5 same-name hit.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (identical to mathlib; `CommRing`).
- Mathlib search (Phase 5): **found in mathlib as `normEDS_ofNat`; identical form**
  at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:293`.
- Composition check (Phase 6): N/A — exact lemma already upstream; 0 by-name call sites.

**Rationale.**
The NagellLutz project's `LutzNagell/EllipticDivisibilitySequence.lean` is a
**fork** of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same
copyright header "David Kurniadi Angdinata", same module docstring, same section
layout `IsEllDivSequence → PreNormEDS → NormEDS → ComplEDS → Map`, same `def
normEDS`). The lemma `normEDS_ofNat` is present in current mathlib at line 293
with a statement **identical character-for-character** to the project's line-897
statement, carrying the same `@[simp]` attribute, in the same unnamespaced
`section NormEDS`. The sole difference is the proof tactic (project uses
`simp_rw [normEDS, preNormEDS_ofNat, Int.even_coe_nat]`; mathlib uses
`simp [normEDS]`), which is immaterial. This is exactly the consolidation-monorepo
"duplicated mathlib file" situation flagged in the project context.

**WHY not (refactor-actionable).**
Mathlib already has this lemma, verbatim and by the same name. The project should
not re-ship it; it should `import Mathlib.NumberTheory.EllipticDivisibilitySequence`
and drop the fork (or, if the fork is staging upstream additions the Nagell–Lutz
development needs — `complEDS₂`, `complEDS`, the `Map`/`Param` sections,
`IsEllSequence.normEDS_of_mem_nonZeroDivisors`, etc. — at minimum delete this
particular lemma so it does not shadow the upstream one). There are **0** internal
call sites referencing `normEDS_ofNat` by name (it is a `@[simp]` lemma, used by
automation), so removing the local copy lets the identical mathlib `@[simp]` lemma
fire in its place with no statement change and no downstream edits.

Existing mathlib decl:  `normEDS_ofNat`
Located at:             `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:293`
Our form follows in 0 lines — it **is** the mathlib statement:
```lean
-- mathlib (line 293), identical statement:
@[simp] lemma normEDS_ofNat (n : ℕ) :
    normEDS b c d n = preNormEDS' (b ^ 4) c d n * if Even n then b else 1 := by simp [normEDS]
```
Call sites in our project (Phase 6.0): **0** by-name (`@[simp]` consumers excluded).
Refactor plan: delete the project's `normEDS_ofNat` (line 897) — and, more broadly,
de-duplicate the forked `section NormEDS` / this file against
`Mathlib.NumberTheory.EllipticDivisibilitySequence` once the project rebases onto a
mathlib carrying everything the fork added. No call sites reference it by name, so
no per-site edits are required; the identical upstream `@[simp]` lemma takes over.

Next action: remove `normEDS_ofNat` from the project as part of de-duplicating the
forked EDS file against `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

---

## Next step

Delete `normEDS_ofNat` from the project and import
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (where the identical lemma
already lives); de-duplicate the forked `section NormEDS` / file against mathlib.
No call-site changes needed (0 by-name uses).
